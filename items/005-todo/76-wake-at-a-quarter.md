005-76. Fix: BufferedStream checks the quarter-full rule only when its thread wakes
==================================================================================

Status: open. Kind: fix. Created 2026-10-29.

Registered at Frans's request (2026-10-29, 09:36, when he set the default
buffer time to 50 ms in 005-64): "Also register a 005 fix for the rest."
Registered only; not implemented.


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
