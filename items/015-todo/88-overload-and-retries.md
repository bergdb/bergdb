015-88. Investigate: transaction retries
========================================

Status: done (2026-11-05): the cap of the retry sleep at 640 ms for
release 2026.3 landed in 8b97f24; the rest of the retries is in 017-06.
Kind: investigate. Created 2026-10-30 as 005-81; split on
2026-11-04 (overload, backpressure and admission control to 017-06);
moved here from 005-81 on 2026-11-05; decided by Frans on 2026-11-05,
14:12: the cap now, the rest moved to 017-06.

## Where the material went

The investigation's sections 1 to 8 moved on 2026-11-05 to
[017-06, transaction retries](../017-long-term/06-overload/retries.md),
as they were and with their numbers: a citation of 015-88 (or 005-81),
section n, is that file's section n. That is: the purpose and scope, what
the code does today with the exact retry policy (section 2.5), the wait
points of a retrying attempt (2.6), the client contract and its draft
(3, 3.1), the retry policies to compare (4), the experiments (5), the
implementation checks (6), the first step and the deliverables (7), and
the harness, the baselines on s1 and their findings (8, with what is
left in 8.9). The harness and its results stay in
[81-overload-and-retries/](../005-todo/81-overload-and-retries/).

The problem, in short: `RwTransaction.executeRw()` reruns a refused
transaction after sleeps of 10, 20, 40 ms and so on, doubling to
10,240 ms, without end; on a hot key a request waited 10.2 s across
eleven attempts (017-06, retries, section 8.5), and a long action under
continued load never commits (section 8.6).

## Frans's decision

2026-11-05, in a discussion with session bergdb-e8. At 13:57 Frans first
considered "Option A": move most of 015-88 to 017-06, keep the sleeps 10,
20, 40 and 80 ms, and then throw an exception to the user code. Then, at
14:09: "Getting cold feet. This may be a more fundamental thing than I
first thought. How about keeping things essentially as is. We could just
change to go to around 640 ms and then repeat there at that sleep time.
Clients today count on eventual success. This is a very small change. I
hesitate. This should always work. It is almost like an
OutOfMemoryException, should never happen. But it can if we have
overload."

bergdb-e8's answer: whether `rw()` can fail is a contract question and
fundamental. Eventual success is already not guaranteed (017-06,
retries, section 8.6: a long action under continued load never commits,
the history case), so today's contract is "succeeds unless overloaded,
and then may loop forever"; whether that shows as a hang or as an
exception is 017-06's question (overload, backpressure, admission
control) and is answered there, with the rest. For 2026.3: only the cap
of the sleep at 640 ms, the contract unchanged, and the Javadoc says
that under overload a transaction may never commit.

Frans, 14:12: "Yes, do it."

## What 2026.3 does

* **The cap.** `executeRw()` sleeps 10, 20, 40, 80, 160, 320 and 640 ms
  after successive refusals, then 640 ms after every further one, in
  place of the doubling to 10,240 ms. Eleven attempts then sleep
  3,830 ms in all rather than 10,230 ms, and a sleeper under continued
  load tries again every 640 ms. No jitter, attempt limit or setting.
* **The contract unchanged.** The call retries until an attempt commits;
  it throws no new exception for overload.
* **The Javadoc** of `rw()` says that under overload a transaction may
  never commit. The release notes keep it as a limit (018-01, D5), not a
  known fault.

Done when the cap and the Javadoc are committed (`BEFORE COMMIT OK`),
with their line in `releases/next.md`. The question whether `rw()` should
ever give up, with option A as one answer, is at the top of 017-06's
retries.

## Log


2026-10-30. Registered and planned at Frans's request. Validated the retry
sequence and shared W/RW call sites, buffer-room and durability waits,
read I/O path, eviction watermarks and timing qualifications, memory
accounting, and existing related work against source. No Java changes or
new benchmark/test runs in this planning step.

2026-11-04. Split at Frans's decision (19:11): "005-81, I like your idea
to split this. So, split it." This entry keeps the retries: the wait-point
map and the client contract they need, the diagnostic harness, the
hot-key and disjoint-key baselines, the retry variants and the
`executeRw()` proposal, its deliverables 1 to 3. The broad question moved
to 017-06: the read, CPU and memory parts of section 2, the admission
points of the contract, the overload workloads, the arrival model, the
recovery measures and deliverable 4. Title, purpose, scope, "Done when"
and first step rewritten for the retries; replication's waits dropped
(removed, 005-11); the mention of 005-07 corrected (dropped; 016-07);
dated notes for 005-47, 005-11 and 005-52 in section 2. The code was not
reviewed again. By Claude (Opus 5.5, Claude Code).

2026-11-05, 07:20 to 08:00. Section 7's first step, at Frans's approval
("005-81 (retries) gets its harness and the hot-key and disjoint-key
baselines, timed on s1."). Built the harness (`RetryBench.java`, from
006-11's), the probe patch (`make-probe.py`), the runner and the
summarizer in [81-overload-and-retries/](../005-todo/81-overload-and-retries/);
built stock and probe jars on s1 from `git archive` of `0c6c4be`; ran 24
hot-key and disjoint-key runs, 6 one-worker references and 12
history-exhaustion runs on s1 (2 vCPUs), then 16 runs with file storage
and durable commits, with a reopen check, and 12 with a probe of the lock
wait and the refusal's reason in `Db`; all checks passed (section 8).
The 10 s hot-key tail reproduces as 11 attempts of accumulating sleeps;
a long action under unrelated writes never commits while the load lasts.
Drafted the wait-point map (section 2.6) and the contract (section 3.1)
for review. No change to `java/`. By Claude (Opus 5.5, Claude Code).

2026-11-05, 14:12. Decided by Frans in a discussion with session
bergdb-e8 (13:57 to 14:12): the retry sleep capped at 640 ms for release
2026.3, the contract unchanged, the Javadoc's note on overload; the rest
of the retries moved to 017-06 (sections 1 to 8, with their numbers, as
retries.md), with Frans's question whether `rw()` should ever give up
under overload. This entry now holds only the cap; status in progress.
006-12's W3, the retry variants on s1 tonight, dropped. By Claude (Opus
5.5, Claude Code).

2026-11-05. Done: the cap landed in 8b97f24, by session bergdb-e8's agent:
`RwTransaction.nextSleep` sleeps 10, 20, 40, 80, 160, 320 and 640 ms, then
640 ms after every further refusal; the Nano test
`RwTransaction.testSleepsBetweenReruns`; the Javadoc of
`Connection.rw(Action)` says it retries until it commits and that under
overload it may never commit; a line in `releases/next.md`. JAVADOC PUB
OK, BEFORE COMMIT OK (106 s). The rest of the retries is in 017-06. By
Claude (Opus 5.5, Claude Code).
