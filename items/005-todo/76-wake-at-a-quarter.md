005-76. Fix: BufferedStream checks the quarter-full rule only when its thread wakes
==================================================================================

Status: done. Kind: fix. Created 2026-10-29. Closed 2026-11-02.

Registered at Frans's request (2026-10-29, 09:36, when he set the default
buffer time to 50 ms in 005-64): "Also register a 005 fix for the rest."
Implementation authorized by Frans on 2026-11-02: "Fix 005-76 as proposed."


The issue
---------

`BufferedStream`'s consumer thread checks `shouldFlush()` only when it
wakes, every bufferTime / 4 (`waitTime`): 12 ms at 50 ms and 25 ms at
100 ms, about 18 and 32 ms on macOS, where a wait lasts longer than asked
(005-13's WaitProbe). One of its rules is the quarter rule: a flush starts
when a quarter of the buffer (2.5 MB of the default 10 MB) is buffered.
But nothing wakes the consumer when an append takes the buffer past a
quarter (`append` notifies only an idle consumer, 005-14, and `flushSoon`
only for a sync, 005-48). So the rule is seen up to one wait late.

At a high rate that costs throughput. At 100 to 170 MB/s of stream, 3 to
5 MB arrive between two checks at 100 ms; a flush takes at most half the
buffer (5 MB), so the buffer keeps filling, and the writer waits for room
when less than a tenth (1 MB) of it is free (`append`'s `wait()`). 005-64's
runs of 2026-10-28 on F53 and s1 (question 1, and question 5's rules
that explain it):

* at 100 ms, with 1 KB values (about 100 MB/s of user data), 13 to 16
  percent fewer puts a second than at 20 ms on both machines (a-1k 105,211
  to 91,748 on F53, 81,609 to 70,601 on s1);
* at 100 ms, a p99.9 append of 16.5 ms on F53 and 24.6 ms on s1 for
  transactions of 100 puts (a-1k-x100), from about 1 and 3.9 ms at 20 ms;
* at 50 ms (the default since 2026-10-29) no loss was measured at these
  rates, but the margin is smaller: 2 to 3 MB arrive between checks on
  F53 at 100 to 170 MB/s of stream (a wait of about 18 ms), and a faster
  writer or disk would reach the limit.

005-13 saw the same at 200 ms (37 percent fewer puts a second with 1 KB
values: "Nothing wakes the consumer when the buffer is full. Not fixed;
it does not matter at 20 ms.").


Proposed fix
------------

An append that takes the buffer past a quarter wakes the consumer: in
`append`, after `appendToBuffer`, a `notifyAll()` when `pStart - cStart`
has just reached `twentyFivePercentOfBufferCapacity` (once per crossing,
not on every append above it, so that a busy writer does not notify for
each transaction). Perhaps also when the writer starts to wait for room,
though a quarter is reached before that. This is work in response to the
call (010-P3): the consumer does not wake more often, it wakes when there
is a reason. Then the buffer time no longer costs throughput at a high
rate, at 50 ms and at longer times; the quarter rule bounds the bytes at
risk as question 5 of 005-64 says, without its "up to one wait more".

The stream's bytes do not change: the buffer time and the flushes decide
only where one append ends and the next begins.


Done when
---------

* The change, with a test that fails before it: at a high rate with a
  long buffer time (say 1 s, so that the timer never flushes in the
  test), the writer does not wait for room (`takeRoomWaits()` or the
  appends' times), where on the code before it does.
* StreamDigest identical against `main` (36 of 36).
* `java/before-commit.sh` (BEFORE COMMIT OK), `java/stress/level2.sh`
  and `java/stress/level3.sh`.
* 005-64's runs (`night/run-f53.sh`, `night/run-s1.sh`) repeated at 50
  and 100 ms on the changed code: no throughput loss against 20 ms (a-1k
  and a-1k-x100's puts a second and p99.9).


First step
----------

The test first: a `BufferedStream` over a stream whose append takes a few
milliseconds (as a force does), a buffer time of 1 s, and a writer of
1 KB appends as fast as it can; count its waits for room. Then the
`notifyAll()` in `append`.


Size and order
--------------

S: a few lines and a test, plus the runs on F53 (quiet) and s1. Builds on
005-13 (the sweep that first saw it at 200 ms), 005-14 (the idle wait,
whose notify in `append` is the model), 005-48 (group commit) and 005-64
(the runs and question 5's rules).


Implementation and checks, 2026-11-02
-------------------------------------

An append now notifies once when `pStart - cStart` crosses from below a
quarter to at least a quarter, including equality. The idle notification
stays. The consumer also checks the quarter before entering its timed
wait: a notification during a flush is not saved, and a half-buffer flush
may leave a quarter ready without any new crossing. A notification alone
would leave both cases waiting for the timer.

Three regressions were added first. All three fail on the previous code
([before-tests.txt](76-wake-at-a-quarter/runs/before-tests.txt)) and pass
with the fix, with assertions on and off:

* An append of 255 bytes followed by one byte in a 1,024-byte buffer wakes
  a consumer already in its timed wait. The timer's wait is 15 s; the
  test allows 2 s for the notification and checks the bytes written.
* A blocked first flush lets another quarter arrive while the buffered
  amount is already above a quarter. After release, the second flush
  starts without a timer wait. A sync request starts only the first flush.
* A writer appends 512 blocks of 1 KB, spaced 1 ms apart, to a 256 KB
  buffer with a 4 s buffer time, over a stream with a 3 ms append delay.
  Before the fix it waits for room twice, for 1,524 ms in all; after, zero
  waits. It checks every byte after closing, across ring-buffer wraps.

`before-commit.sh`: BEFORE COMMIT OK, 1,093 unit tests and 78 f-tests.
Full `level2.sh`: LEVEL 2 OK, 70 conformance traces. Full `level3.sh`:
LEVEL 3 OK, 25 reclaim conformance traces, 440 cold recoveries under the
power-loss model, and 60 s of interrupt stress. Level 3 ran on an
isolated copy of the candidate sources, to avoid rebuilding Level 2's
classpath while it ran; all 464 input files compared byte for byte with
the working tree afterward. The summaries are preserved in `runs/`.

The preserved before/after snapshots include the pre-existing, unrelated
Reclaim worktree change on both sides; this task changes only
BufferedStream's Java code. Only the changed snapshot was timed in these
performance runs; the earlier measurements cited above are historical
005-64 results. The digest reference is committed `main`, `afc3d20`.

StreamDigest's 36 logical streams are identical: length, decided retained
position, first available lookup time, and SHA-256 from the decided cut.
The strict comparison reports 35 of 36 identical, because `l3-node62
reads` physically cuts at 8,000,000 in the reference and 9,000,000 after
the fix; both decide 9,164,760 and have the same retained bytes. Physical
cuts depend on flush timing (005-72), which this fix changes. The raw
outputs and both comparisons are preserved in
[runs/](76-wake-at-a-quarter/runs/); this is not a claim that physical
cut positions or hashes including already-reclaimed bytes are identical.

The performance check uses 005-64's runners and harness, restricted to
the two workloads named in this entry's completion criteria: `a-1k` and
`a-1k-x100`, at 20, 50 and 100 ms. Their six original suite lines are in
[throughput.suite](76-wake-at-a-quarter/throughput.suite).
[mixed.txt](76-wake-at-a-quarter/mixed.txt) is intentionally empty; mixed
and durable writers were not part of this fix's performance criterion.
Three rounds rotate the buffer-time order, 20/50/100, 50/100/20,
100/20/50. The s1 run uses an isolated new directory,
`/opt/bergdb-bench/005-76-20261102`, a 2 GB heap and FORCE=0. F53's timed
runs follow the correctness checks, with no overlapping test work.

F53's wrapper is [run-f53.sh](76-wake-at-a-quarter/run-f53.sh), taking
`BUILD=005-76-after-20261102`; preparation used 005-64's
`night/prepare.sh` with that BUILD and CLONE set to this repository. Its
initial attempts were refused at the 90 % idle admission check, including
after adding a 30 s cooldown after the force probe. The actual admitted
rotations ran the same `performance.sh reference` directly, with its quiet
check enforced, FORCE=0, the same CPU agent, G1 and an 8 GB heap. The first
round's setup was traced to investigate the refusals; it admitted at
92.29 % idle. No timed run overlapped another run from this task. All
refused attempts are preserved, along with the admitted sessions, in
`runs/`; they are not included in the metric tables.
For s1, the same preparation made the package, whose `night/bufftime.suite`
and `night/mixed.txt` were replaced by the two files above before invoking
005-64's `night/run-s1.sh`, with ROUNDS=3, BUDGET=0, the new REMOTE above
and OUT set to this entry's `runs/s1/`. Its check parsed all six rows,
three runs per row. The JSON metric records were fetched separately from
the original `write.result.json` files. `summarize.py` makes compact tables
from those records; all other metrics remain in the JSON, and the full
sessions remain in Java's ignored build directory on each machine.

s1's results
------------

All three rounds started at 100 % idle CPU, with FORCE=0. Medians:

| workload  | buffer ms | puts/s | append p99.9 ms |
|---|---|---|---|
| a-1k      | 20  | 81,422 | 0.055 |
| a-1k      | 50  | 80,209 | 0.061 |
| a-1k      | 100 | 78,372 | 0.063 |
| a-1k-x100 | 20  | 86,511 | 3.736 |
| a-1k-x100 | 50  | 87,018 | 3.228 |
| a-1k-x100 | 100 | 88,022 | 3.916 |

At 50 and 100 ms, single-put throughput is 1.5 and 3.7 % below 20 ms;
the three-run ranges overlap. The 100-put workload is 0.6 and 1.7 %
faster. The earlier 13 to 16 % throughput penalty at 100 ms is not
reproduced. Its 100-put p99.9 is now 3.9 ms, versus 24.6 ms in 005-64;
it stays within the current 20 ms runs' range, 2.5 to 4.5 ms. This is a
comparison with the historical report, not a new before/after benchmark
on the same base commit. Full ranges and raw metrics are in
[runs/s1/](76-wake-at-a-quarter/runs/s1/).


F53's results and outcome
-------------------------

The three admitted rounds started at 92.29, 93.40 and 91.74 % idle CPU,
with FORCE=0. Medians:

| workload  | buffer ms | puts/s  | append p99.9 ms |
|---|---|---|---|
| a-1k      | 20  | 101,453 | 0.029 |
| a-1k      | 50  | 102,116 | 0.029 |
| a-1k      | 100 | 103,485 | 0.029 |
| a-1k-x100 | 20  | 109,714 | 1.270 |
| a-1k-x100 | 50  | 112,021 | 1.073 |
| a-1k-x100 | 100 | 110,882 | 1.139 |

At 50 and 100 ms, single-put throughput is 0.7 and 2.0 % above 20 ms;
the 100-put workload is 2.1 and 1.1 % faster. There is no measured
throughput penalty at the longer buffer times. Its 100-put p99.9 at
100 ms is 1.14 ms, versus 16.5 ms in 005-64's historical report. The full
ranges and raw metrics are in [runs/f53/](76-wake-at-a-quarter/runs/f53/).
Both machines' checks parsed all six rows, with three runs per row.

Closed: the crossing notification and pre-wait quarter check fix the
polling delay, the regressions fail before and pass after, the full
correctness checks pass, and the performance runs no longer reproduce
005-64's 100 ms penalty. The StreamDigest completion criterion is met for
all 36 logical streams from the decided cut; the one physical-cut
difference in the strict comparison is documented above, not suppressed.
The buffer time stays 50 ms. No API or format change; C unchanged.
