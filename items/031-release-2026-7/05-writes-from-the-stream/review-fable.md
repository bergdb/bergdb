# Review of 031-05, every write a function of the stream and the actions

By an independent reviewer (an agent on Fable, high, at Frans's request),
2026-11-26, in a clone (branch `031-05` at `4135ba2a`, `java/` at `8a6bb105`). Nothing is
committed. My probes and logs were kept outside the repository (throwaway:
`ReviewProbe`, `TornProbe`, `ConcProbe`, `UpGen` and `UpCheck`,
`CvarProbe` with `variant-c-Db.diff`). "Ran" means I ran it here, on a
loaded machine; "read" means code reading only.

**Verdict.** Take the direction, as D2. At record boundaries the
prototype does what the study says: I could not make it write a byte that
the stream and the actions do not decide. But D2 as built fails an f-test,
section 4 claims more than holds (a crash inside a record), the Lean
theorem is false as written, and one small change (the start writes what
is due) would remove the held clock between calls and about a third of
the new code.


## 1. Findings

**F1. D2, the design recommended, does not pass `before-commit.sh`.** Ran.
* Where: `Db.setRetainDuration` and `setReclaimInternalFraction`, the
  line `if (Reclaim.eager) reclaim.catchUp()`.
* What: with `-Dproto315.eager=true` the f-tests give 2 failures of 90:
  `ReclaimRetentionTester.testRestartWithOtherRetention` ("Expected
  187000001, got 219500001") and `databasesStopped` as its consequence.
  In D1, the default, the 90 pass. The unit tests pass in D2 (1,755, also
  with `-Dtranscheck=1`), and so do the count gates.
* The case: a restart, then `setRetainDuration(2 s)`. In D2 the setter
  decides a cut in its own call, so the first available lookup time moves
  at the setter; on `main` and in D1 it moves at the next commit.
* A behaviour to decide, not a fault of the mechanism: the setter cuts
  at once (the test changes), or nothing is due after a settings record.

**F2. A crash inside a record does not leave a prefix of S.** Ran.
* Where: sections 4.1 and 4.4 ("the stream is the prefix before it").
* What: recovery completes a torn record as an aborted one, which stays
  in the stream, so every later record has another position.
* The case, `TornProbe`: the last record cut by 1, 9, 40 or all but one
  of its bytes, a start, the rest of the actions. 0 of 1,038 continued
  streams equal the uninterrupted run's; with the whole record removed,
  261 of 261 do. The continuation is still a function of the torn
  stream: 1,468 of 1,468 the same with and without a later restart.
* So the statement holds at record boundaries, as Frans worded the goal.
  A torn record is an input, like the creation.

**F3. "The stream after the call is S" also fails in D2 after a crash,
and the Lean equality with it.** Ran, and read.
* The case: seed 22, D2, a crash right after the last user record. Its
  maintenance stays due; the stream is a record short (1,478,488 of
  1,480,928 bytes) until a next call. Section 4.2's point 2 ("a prefix")
  covers it; point 1 and `T16_crash`'s `=` do not.

**F4. An interrupted or handed-over `maintain()` is not "the same call
with a smaller budget", nor "two calls with the same time".** Read; ran.
* Budgets are whole units of 1,000 above a floor of 100, so a call ended
  after m parts is in general no public call (the probe uses
  `maintain(budget, maxParts)`). After a handover the call keeps a time
  earlier than the commit between, which no application call has; it
  breaks the sketch's `TimesMono`.
* The bytes can differ only through `now` in M5 and M6. `ConcProbe`
  replayed 6,606 continued segments as new calls: the same stream.
* Simpler: the part is the unit. An action is a transaction, a setter, or
  a part with its call's time; `maintain(b)` is the parts that fit. A
  crash inside a call, the handover and the budget then need no rule.

**F5. In D2 the clock stays held after a crash or a stop until the next
write, without bound.** Ran.
* Where: `Db.holdIfDue` at the end of a start; section 10 calls it
  "short and rare".
* The case: 41 of 393 and 30 of 343 record boundaries (about 10 %) leave
  maintenance due. A database started there and only read returns the
  last transaction's time from `currentTime()` as long as it runs, and a
  relative time ("-10 s") resolves against it.

**F6. Q2 (c), the start writes what is due, is simpler than D2 as
built.** Ran (`variant-c-Db.diff`: 4 lines in the start, and counters).
* The same stream at all 736 boundaries, crash and stop. No call's
  catch-up before its own record wrote anything (D2: 40 and 30). The
  clock was never left held after a call or a start (D2: 41 and 30).
* The rule becomes: every call, a start too, leaves nothing due. These
  can then go: the catch-up before a call's own record (four sites),
  `holdIfDue` with `catchUpDue`, `safeDue`, `cutDue` and
  `commitWork(false)`, and the D1 switch; about 80 to 100 of 231 lines.
* P2's "a refused request must leave the stream unchanged" stays true
  (Q8 contradicts it), and a call's first record is always its own,
  after a crash too, which is what `TraceExport` assumes.
* The cost: a start appends up to one commit's maintenance; a read-only
  start cannot and need not. F1's test fails here too.

**F7. `catchUp()` runs outside the code that fails the database.** Read.
* Where: `Db.executeLocked` (its try catches `Error` only),
  `maintainInner` (before the try around `maintainPart`), `maintain`'s D2
  tail, `setStartupDistance`, `Reclaim.setSettings`.
* On `main` this ran inside the commit's go point, where any exception
  fails the database (P7). Now an exception between a change of
  reclaim's memory and its record (`table.rows.add` then `storeTable`;
  `pSafe`; `cut`) reaches the caller as a refusal, with memory ahead of
  the stream. Read errors fail the database by themselves, so I found
  no case to run: it takes a bug, or "no database time left".
* The "would write" predicates are copies of the writers, kept alike by
  hand; a `step()` that returns without a record leaves the clock held.

**F8. The dropped after-row charge re-opens 028-26**, fixed on
2026-11-19: 6 % less charged at the default node size, 26 % at node size
8 (the study's figures). Read. An option not in Q3, not verified: the
row's `rewritten` at a fixed width, patched after the batch (`putKvs`)
and before `store()`: one record, the exact charge.

**F9. G4's M5 is a klong or two from its limit**: 29 of 15, 1.933 of 2.0
(031-04: 1.429). Ran in D2: `COUNT GATES OK`, the study's figures. Not
explained by the study or by me. G5's 179,456 bytes kept is far from its
limit (0.18 of 1).

**F10. The format changes, though no record's does.** Read. A done row
now comes first in the current row; `main` and 2026.6 skip a done
current row at a start (`!c.done`), so an old writer on such a stream
redoes the iteration from the table's row. It belongs with 031-04's Q8.

**F11. Small gaps in the wording.** Read. The draft P2 drops "the same
initial stream and stream-affecting settings": the step reserve, the
node size and the key are inputs too. The goal holds at the Core's `Db`:
the Pub's index jobs (N9) are Core actions that BergDB's own threads
issue, also after a restart. And the clock is held for a whole
`maintain()` call, its dead hand, waits and sync too.

**What held.** All ran; 0 hold failures in every run.
* My own search of the writers found the study's three append sites and
  no other; no thread commits but the Pub's two jobs.
* `ReviewProbe`: 7 configurations, D2 and D1, a crash and a stop at every
  record, 11,430 continuations, the same stream but F3's two. With a
  reader's `currentTime()` just before every call; a refused call before
  every call (in D1 it writes the maintenance, and crashes inside it); a
  clock that goes back (little reclaim ran there) or stands still; a
  clock that jumps up to 40 ms after the action's time is taken (the
  same digest as without).
* Eviction at every transaction: the same digests as without it, and
  3,188 more continuations the same.
* `ConcProbe`, 10 runs, D2 and D1: 2 to 4 writer threads, 1 or 2
  `maintain()` threads, a setter thread, readers (15 to 23 million reads
  a run), 3 or 4 `stop()` calls from another thread, each with a
  restart; 20,000 to 126,000 commits and up to 15,949 parts a run. One
  thread then replays the logged actions at their times: the same
  stream in all 10, up to 483 MB.
* Upgrades: 427 streams of `main` (`27548f13`) and 427 of 2026.6, each
  crashed at a record, started on the prototype and continued. No start
  threw or appended, every key had its value, and 2,119 crashes after
  the upgrade for each source continued to the same stream, D2 and D1.


## 2. Answers

**1. The wording.** Right in substance at record boundaries. Change: a
torn record is an input (F2); point 1 is a prefix that the next call, or
start, completes (F3); the part is the unit of `maintain()` (F4); a
refused call "adds nothing of its own", or (c) (F6); the settings and the
layer (F11). Several writer threads need one clause: the order is the
write lock's. Readers and times are right as written.

**2. The inventory.** Complete for what appends; no input beyond N1 to
N10 but F11's settings and F2's torn record.

**3. The prototype.** It achieves the goal at record boundaries, D1 and
D2, under all I tried; not inside a record (F2); not yet a gate (F1).

**4. D1 against D2.** D2 is right: D1 holds the clock between all calls,
refuses read-modify-writes and breaks the tools. D1's one merit is that
its catch-up path runs at every call; D2's runs only after a crash.
Variant (c) is simpler than both (F6), and I recommend it, given
Frans's decision on a start that writes. Maintenance inside the user's
own record would end the question, but redesigns the step: not now.

**5. Costs and risks.**
* N6: not to land as it is (F8). N4: fine inside calls; between calls
  only with (c) (F5). Gates: F9.
* P1: one record a part makes the handover finer. Not measured:
  `timing.sh`, the pause probe, 031-04's 10M runs. One thread, 600,000
  puts: 13.8 to 14.5 µs a commit in D1 and D2 alike (ran, indicative).
* Complexity: 231 lines, no recovery case, no state in the stream. The
  risk is in the copies (F7) and in two modes: drop D1 before more
  review.

**6. The Lean sketch.** Sound only with changes; feasible. Checked by a
second agent against lean/, spot-checked by me (`T2_restart`, `RunOK`,
`T12_restartCut`). The citations exist.
* `T16_crash`'s `=` is false at a schedule's end (F3): state it after
  the due loop has run on both sides, or as a prefix.
* A record is a transaction in the model, so a crash after any record of
  a given list is `T2_restart` already. New is that `due` chooses the
  list; the proof is an induction over `T2_strong` and `restartCut_rel`.
* With cuts the conclusion needs `cutStream`, and `due` must be unchanged
  by a cut and by `SameFrom`; T12's hypotheses are missing. `DueMono` is
  undefined, and B or S is not monotone. `StepsOK` needs Mathlib.
* In plain words: it would prove that if maintenance is chosen by a
  function of what a start restores, crashes at record boundaries change
  no record. That Java's `catchUp` is such a function stays tested: the
  model has no times, bytes, budgets or clock. Reduced, not proved;
  600 to 1,100 lines is likelier than 1,600.

**7. Q1 to Q9.**
* Q1: (a), with answer 1's changes.
* Q2: (b), and (c) on top of it (F6).
* Q3: (a) for the study only; before a landing (b) or F8's option,
  measured with G1 to G4.
* Q4: (a) now, (b) as an item; the wording names the layer.
* Q5: (a), with the other builder inputs (F11).
* Q6: (a); with (c) the hold is only inside calls.
* Q7: yes, and the part as the unit (F4).
* Q8: accept under (b); it disappears under (c).
* Q9: after the design lands, the statement corrected first.

**8. Overall.** Yes. Maintenance decided from the stream's last record
and timed from it is a sound and small idea, and it survived every
attack at record boundaries. Change first, in this order:
1. Decide F1 (what a setter leaves due); D2 passes `before-commit.sh`.
2. Decide (c). If yes, delete D1, the catch-ups before a call's record
   and the "would write" copies; `catchUp` inside the failing code (F7).
3. Correct section 4 (F2, F3, F4, F11) before any wording goes to 010.
4. Decide the after-row charge (F8); explain G4's M5 (F9).
5. Then `night.sh`, `level3.sh`, `level4.sh`, `timing.sh` in that
   design, and Codex's review.

Not done by me: the cause of F9, timing, the Pub layer under kills, a
crash between a record ending at a meta block's position and the block.
