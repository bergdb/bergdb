# 024-35. A sweep for open work forgotten for 2026.5

Created 2026-11-12 by Frans Lundberg. Status: done (2026-11-12), read
only.

Frans, 2026-11-12, 14:12: "Start a new agent to search for other open
things we have forgotten that should be included in the release. Just a
double-check." What is open, meant for 2026.5 (or a bug or known issue),
and neither done, decided nor moved, beyond what 024-28 (the checklist,
10:37) and 006-23, section 5 (the day's decisions and landings to 14:16)
already hold. Read only, at `main` `af6efacb`; by the agent "sweep" of
coord-1112, 14:12 to 14:25.


## 1. In short

Two bugs are still open for 2026.5, and the release notes lack most of
today's work:

* **OT2:** 2026.4's notes promise "the fix is for 2026.5", and it is not
  made. A 43-line patch is ready.
* **CA3:** a Core put can make a database that never opens again. By
  today's rule R5 that is a bug.
* **`releases/next.md`** does not mention 024-31 to 024-34 or the new
  `maintain()` API. Its Known issues have one entry, where 2026.4 had
  about twenty.

Everything else is small, or already covered by 024-28.


## 2. Findings, most important first

"Rec" is the recommendation.

1. **OT2, the Linux "directory in use" race** (024-01, 11.2; 006-17,
   section 6; 2026.4's notes, Known issues: "The fix is for 2026.5").
   `FileStream.unlockDir()` still closes `bergdb.lock` before it removes
   the keys from `LOCKED_DIRS` (`FileStream.java:955`; no commit to the
   file since 2026-11-09). So a new database in a new directory can,
   rarely and on Linux, be refused as in use. Only the test half went
   in (`85bed824`). The product fix is
   `/Users/f/fl/bench/2026-11-10/jdk17-f/product-fix-idea.patch`, 43
   lines: close the file and remove the keys under the `LOCKED_DIRS`
   monitor. With it, s1's probe went from 10 failures in 30,000 tests to
   0. Aim 1, and a promise in the last notes.
   **Rec: do before the candidate** (small; before-commit, level1); s1's
   probe in the release night. If it is left out, the notes must say
   again that it is not fixed.

2. **CA3 / C-U2-8, a Core put under the Core's own keys** (024-01, 5.3;
   020-11, section 11; 022-06-2, U2-8, confirmed in Java). Seven bytes
   put under `/#i/dreclaim/-settings.txt` are accepted. After that,
   every start fails with `InternalDataException` and nothing can repair
   the database. Since 13:24, 010-04, R5 reads: "A call of the Core API,
   whatever its arguments, keeps the integrity of the Core's key-value
   store ... its availability." That makes CA3 a bug of 021-27's class.
   024-01 rated it S, low risk, "refuse them". `maintain()` (024-32) now
   also writes under `/#i/dreclaim/` (its filler key).
   **Rec: Frans's word now.** Then either do it before the candidate (the
   Core refuses a caller's puts and deletes under the keys it writes
   itself, `/#i/dreclaim/`; internal writes pass), or name it in the
   notes as a known issue and as an open case of R5.
   **A related R5 question:** a value transformation whose result passes
   8 MiB, or that throws, fails the database. That is `Db`'s Javadoc
   (L4, 015-51) and next.md's "Limits". R5 says a database fails "never
   for a caller's misuse of an API". **Rec:** Frans rules whether
   user code inside a commit is the user's, as for `Action` (QR1). Then
   it is either one more line in R5's cases or a case for 026.

3. **`releases/next.md` lacks today's landings** (its last code entry:
   021-27, with Q27-1 at 14:16). Missing:
   * 024-31: the take's pace capped after a decrease of the startup
     distance (OP4; the largest record halved at 10M keys, the catch-up
     4.5 times longer). It changes 2026.4's limit "A decrease of the
     startup distance at 50M keys ... 13 to 15 MB".
   * 024-32: `Db.maintain()` and `Database.maintain()`, **a new public
     API in the Pub layer**: what it writes, false when nothing is due,
     the sync. Also G5 under "Tests and gates", and the two new
     conformance configurations.
   * 024-33 (ST6: the cache's tables shrink; the floor of about 256 kB)
     and 024-34 (OP8: a step's second reads halved, no byte changed).
   * QF1 (Frans, 14:07): the fraction stays 1/4, and the bound that G3
     holds (the stream kept at most 6 times the live data beyond the
     history) stated for users.

   **Rec: do before the candidate.** Commit A carries the notes (024-28,
   section 7, steps 2 and 4).

4. **next.md's "Known issues and limits" has one entry; 2026.4's has
   about twenty** (`releases/2026.4/readme.md`, Known issues and
   limits). None of them is restated as fixed, still so, or changed.
   * Fixed or changed: a leaf's dead entries (by the merges and theta,
     024-21 and 024-23); the long key's quadratic loop (gone with the
     111-byte limit, L2); `getTrans` inside a record (021-27); the time
     klong (`90184540`); the decrease at 50M keys (024-31).
   * Still so: dirty top nodes after a mass delete (fix (a) dropped);
     OT2, unless item 1 is made; a transaction larger than the startup
     distance; Core writes the rules leave undefined, with CA3; the API
     wishes; the record header with no checksum; the readers a core
     allows; collectors; overload; D's loose bound; T4 and a cold start.
   * New in 2026.5:
     * aim 4's open proofs, as decided at 12:22: TP30 to TP33, TP7,
       TP10, T4, and TP11 refuted as stated, with 024-12's keyWf to
       follow;
     * ST6's floor of about 256 kB after back to empty (024-32,
       section 7);
     * ST7 closed as negligible;
     * ST8's 10 MB buffer and P8's lag after a mass delete (4.4 R in G4),
       both moved to 026;
     * OP5, a named allowance;
     * next.md's own "Not yet measured: 10M keys, memory, reads" for
       theta.
   * Not raised again: 020-11, section 11's 18-O2 (a job's status lags
     its index) and the index jobs' threads (18-O1).

   **Rec: do before the candidate**, with item 3.

5. **QF3, "the curve documented"** (024-05, QF3, decided 12:46: "a put's
   bytes stated as a function of sd / K; the default sd fixed; the curve
   documented"; 006-19, section 8, point 2; 017-11, 3.2). Not found:
   `docs/levels.md` has only the figures at 10M keys for 50, 200 and
   1000 MB, and 2026.4's notes say only "the default startup distance
   (50 MB) suits up to about 10M keys".
   **Rec: do before the candidate** (docs only): the scale law in
   levels.md and one line in the notes' limits.

6. **No performance comparison against release 2026.4.** Before its
   release, 2026.4 ran `performance.sh`'s quick suite against 2026.3
   (020-12: "the Core unchanged (NO ALERTS)"). For 2026.5, which brings
   format 7's merges, theta, CRC32C, the limits, the pace cap, OP8, ST6
   and `maintain()`, none was found. The only one is 024-33's `ab`
   against a commit of `main`, and 024-28, section 7 has no such step.
   **Rec: do in the release night**: A against `release-2026.4`, quick
   suite, a timing run (both slots). Name any figure more than 10 %
   worse in the notes.

7. **Q34-1, a keys-only scan for reclaim** (024-34, section 6). It waits
   for Frans. 024-34 recommends (b), which changes stream bytes and
   reclaim's pacing. It is not decided and not in 026.
   **Rec: move to 026**, with 024-29's work on the fraction. It is not
   for today's candidate.

8. **024-02 "kept current with the code"** (024-04, section 5), last
   changed at 08:14. It does not name `maintain()`'s writes: the filler
   key `/#i/dreclaim/-fill`, the empty record whose take moves the
   startup position (024-32, 2.4), and the take's cap after a decrease
   (024-31).
   **Rec: in the release night** (items only); it does not hold up the
   candidate.

9. **Two unit tests still wait with no timeout** (006-17, section 6.3,
   point 10; 024-01, TT4, "hangs first"). They are
   `PubTesterOutput.java:190, 198, 201` and `PubTester.java:788, 804,
   808`: `waitForEvent()` and `join()` with no limit. A failure there
   hangs a night step instead of failing it.
   **Rec: before the candidate if an agent is free** (a tests-only fix,
   `waitForEvent(long)` exists). Otherwise nothing.

10. **020-29's Lean proof of the indexes is now only in a bundle.**
    That proof (5,231 lines, "keep on its branch", 024-01, LM3; cited by
    2026.4's notes) lived on a branch in a clone. Today's cleanup
    removed the clone, and the branch is now only in
    `/Users/f/fl/bench/archive-branches/2026-11-09_clone-l29-020-29-index-proof.bundle`.
    The main repository has no ref of it.
    **Rec:** fetch it into the main repository as a branch (Frans's ok).
    This is not a release step.

11. **The release night's confirmation run.** 2026.4 ran 021-25's
    workload on A to show its main known issue fixed (020-31, section
    4). The same for 2026.5 would be 024-07's queue in time order: 1M
    keys and a 256 MB heap, the `OutOfMemoryError` case of 2026.4's
    notes.
    **Rec: in the release night, if there is room**; otherwise nothing.

12. **Housekeeping that the notes' "Open at the release" reads.** These
    are items-only edits by the coordinator, before the candidate.
    * 015's Open table:
      * 015-84 is still "open", though 024-31 made it;
      * 015-18 is still open, though superseded (024-01, TT5: "close");
      * 015-03 is listed as done but still sits in the Open table.
    * 021's readme still gives 021-27 as "waiting".
    * Several 024 statuses still say "on a branch, not on `main`":
      024-09, 024-15, 024-30, 024-31 and 024-32.


## 3. Checked; nothing new beyond 024-28 and 006-23

* 019-todo: nothing open. 021-todo: only 021-27, done today.
  017-07: no entry marked for 2026.5. 017-11: "not for 2026.5".
* 022, the C clone: 2026.5 promised nothing but 024-10, section 10's
  list "when C is taken to 2026.5". Whether it follows is Frans's
  (024-28, section 8).
* `news.md` and 006-22's "For Frans to decide": each point is answered.
  The key klong patch was not applied, by Frans's "best effort" (07:26).
  Nothing hangs.
* 006-21's points: 024-02's Q14 and Q16 and the versioning rule are in
  024-28, section 8, or in 026.
* 024's other questions (024-02, 024-08, 024-10, 024-11, 024-14, 024-16,
  024-18, 024-19, 024-21 to 024-25, 024-29, 024-32): decided, in 026, or
  in 024-28, section 8's list that does not block. One exception:
  024-16's G4 (KR-lit, a stale index entry after `${transactionTime}`
  over a guessed key). It has no entry of its own, as QS5 asked, but it
  is a 2026.4 known issue ("later: an insert-if-absent"). Rec: restate it
  under item 4.
* The release scripts of 2026.4 (`/Users/f/fl/bench/2026-11-10/rel/`,
  `morning/`, the Android scripts) survived today's cleanup.


## 4. State

2026-11-12, 14:25, by the agent "sweep" of coord-1112. Read only at
`main` `af6efacb`; nothing built, run or committed; only this file
written.

* **Done:** sections 1 to 3. These were read: 024-28; 006-23, sections
  3 and 5; 024's readme; 024-04, sections 4 and 5; 024-05, section 7;
  the question lines of every 024 subitem, by grep; 024-01, sections
  5.3, 11.2 and 13; 024-32 and 024-34, State; 015, 019 and 021, their
  Open tables; 017's 2026.5 lines; 022's readme; `releases/next.md`;
  2026.4's Known issues; 020-11, section 11; 020-31, sections 2 to 6;
  006-17, 6.3; 006-21 and 006-22, Outcome; `news.md`, top; 010-04, R5;
  the code at `FileStream.unlockDir` and `Db`'s limits Javadoc.
* **Not done:** 024-03, 024-06, 024-12 and 024-13 in full; whether
  `night.sh` steps are ready for format 7 (024-28, section 7 has this).
* **To continue:** items 1 and 2 need Frans's word or an agent before
  the candidate. Items 3 to 5 are writing for the coordinator or an
  agent. Item 6 is a step for the night's plan.

2026-11-13. Status set after the release (coord-1113).
