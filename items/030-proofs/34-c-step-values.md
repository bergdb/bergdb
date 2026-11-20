# 030-34. C-STEP checks the values a step writes back

Created 2026-11-20 by Frans Lundberg. Status: done.

030-33's finding F1: the model of reclaim's steps (`StepTx`,
lean/contract/Contract/ReclaimSteps.lean) and the trace checker's C-STEP
(030-27) require that a step puts again every old key its scan meets, but
not that it writes back the value it read, nor that it puts or deletes
nothing else. Java copies the value it read (`Reclaim.step`: each KV of the
scan's result is put with its own value, `b.putLongKey(kvt.key, null,
kvt.value, null)`). Frans decided (2026-11-20) to fix the checker now; the
Lean statements are another task. This item is the checker's part: C-STEP
checks the values and the step's other operations. Nothing under
lean/contract/ changed. Done by an agent, on the branch
`030-34-c-step-values`.


# Result

- **STEP-values** (new): each put of a step at an old KV that its scan met
  (a live key in the step's range up to L' whose value node was made
  before c) writes the value the scan read: the key's value after
  T(i - 1), the step's state, as the tree model reads it from the trace
  (the value's hash, as on V and OP lines, 027-02). C-STEP had the value
  nodes; it now also takes their values from the model's scan
  (`liveKeysAt`).
- **STEP-ops**, stronger: besides distinct keys and a put, the step's
  operations are the rewrites of the old KVs met (STEP-puts: every one of
  them; STEP-values: each with the value read) and one put more, the row;
  no other put, and no delete (`OP D` or `OP N`).
- **The row's key.** The trace does not name it, and the trace format is
  unchanged: C-STEP takes it from the trace's first step, the key of its
  one put that is not a rewrite with the value read (the one at a key that
  is not an old KV met, if there is exactly one; else, if the step's only
  such put is at an old KV met, that one), and checks that every later
  step puts at that key. A step may put the row at a key it met with an
  old value (Java's row is a key of BergDB's own, `/#i/dreclaim/...`, and
  the scan meets BergDB's keys as well as the user's); its put then writes
  the row, not the value read. So the check does not depend on the row's
  name, and a step with one put too many, or a rewrite with another value,
  fails in every step, the first included (the first step then has two
  puts that are not rewrites with the value read).
- **On the traces:** level 3's reclaim and crash sets pass (section 3); the
  fault test's three new faults fail by their check's name.
- **No finding about Java:** every step of every trace writes back the
  value it read and nothing else than its rewrites and its row.
- **What it does not cover.** Values are compared by the trace's 63-bit
  hash, not as bytes (030-33, F2). The row's own value (the serialized
  row) is not compared with anything; the STEP line, from the row in
  memory, is checked as before. The Lean model of the steps (`StepTx`) is
  unchanged by this item: that the step's values are the values read is
  checked on Java's traces, not yet a premise of the theorems.


# 1. The check

lean/Check/Steps.lean, `reclaimStepFailures` (per STEP line) and
`stepCheck` (keeps the row's key over the trace). Per STEP line in TX i,
with `old` the KVs met whose value node was made before c, each with the
value read:

- `others`: the step's puts that are not at an old KV met with the value
  read there;
- the row: the trace's row key if known; else, in the trace's first step,
  the key of the one put of `others` at a key that is not an old KV met,
  or, if there is none, of the one put of `others`;
- STEP-values: each put of `others` at an old KV met, but the row's;
- STEP-ops: each put of `others` at another key, but the row's; every
  delete; no row found, or no put at the row's key.

Nine `#guard` tests in Steps.lean (five new) check a rewrite with another
value, a put of a key met whose value is not old, a delete, a step without
the row, and the row at an old key met, at every `lake build`.

The report line of C-STEP reads "old KVs met and checked put again with
the value read" (TraceCheck.lean); `conformance.sh` and `apptraces.sh`
sum it as before (their regular expressions are unchanged) and print the
same words.


# 2. The fault test

lean/test-traces/step-faults.sh, three faults more, each in the second
step of the good trace with three puts or more (TX 101), so the row is
known from the first step:

- **value**: the put of its first user key (a key of one segment; the
  row's has four) with the value 12345: a rewrite with another value.
- **del**: an `OP D` line added, of the key of the first user key's put
  of the next such step (a key that reclaim rewrites later).
- **put**: an `OP P` line of that key added, with the value 12345.

Output (the three new lines, cut at 110 characters):

    value: fails, STEP-values: T(101) the put of the old KV [25684921473302568] writes the value 12345, the scan read 7
    del: fails, STEP-ops: T(101) 1 deletes: [[25684921474236464]]
    put: fails, STEP-ops: T(101) 1 puts neither a rewrite of an old KV met nor the row: [[25684921474236464]]
    STEP FAULTS OK

The fault `nextkey` (030-27) now fails STEP-ops too, before its
STEP-chain: a step whose L' is its L meets no KV, so its rewrites are
puts neither a rewrite of an old KV met nor the row; the test checks
STEP-chain among its failures, as before.


# 3. The runs

At fd7fefd9 (the check, the fault test and the scripts):

- `sh java/before-commit.sh`: BEFORE COMMIT OK (85 s).
- `sh java/stress/level2.sh`: LEVEL 2 OK.
- `sh java/stress/level3.sh`: LEVEL 3 OK; its step 8:

      C-STEP's fault test: 17 faults found, STEP FAULTS OK
      conformance: traces: 35, TRACECHECK OK: 35; C-CUT 0 of 775 CUT lines
        fail; traces without a cut: 0
      C-STEP: 0 of 21483 transactions fail; 1014 STEP lines, 907 iterations
        (906 ended by a step with eod), 11943 old KVs met and checked put
        again with the value read, 775 CUT lines with their iteration's
        last step; traces without a STEP line: 0
      across restarts and crashes: traces: 15, TRACECHECK OK: 15
      C-STEP: 0 of 6837 transactions fail; 503 STEP lines, 309 iterations
        (307 ended by a step with eod), 7745 old KVs met and checked put
        again with the value read, 256 CUT lines with their iteration's
        last step; traces without a STEP line: 0

- `sh java/stress/apptraces.sh night`: APPTRACES OK (C-STEP: 0 of 415
  transactions fail; 2 STEP lines, 6 old KVs met).

So on 1,517 steps of level 3 (19,688 old KVs met), every rewrite writes the
value read, and no step puts or deletes anything else than its rewrites
and its row.


# 4. For 030-26

030-26 should get, in section 4 ("Reclaim's arithmetic and Java's steps
are tested") and in section 5, item 11, after "C-STEP, 030-27":

> Since 030-34 (2026-11-20) C-STEP also checks that each step writes
> back, at every old key its scan met, the value the scan read (by the
> trace's value hashes, F2), and that it puts nothing else than those
> rewrites and its row and deletes nothing; the model of the steps
> (`StepTx`) does not yet require it (030-33, F1).

The page's note "Under correction" keeps F1 until the Lean statements are
corrected.


# Files

- lean/Check/Steps.lean, lean/TraceCheck.lean,
  lean/test-traces/step-faults.sh, lean/README.md,
  java/stress/conformance.sh and java/stress/apptraces.sh (the words of the
  sum). Nothing under lean/contract/; no file of statements.pin.
- 027-02 (section 4, C-STEP), 027-13 (REWRITES, section 9), 030's readme.


# Log

2026-11-20, 16:25. Started, on the branch `030-34-c-step-values` from
bf9b3428.

2026-11-20, 16:40. The check and its fault test (fd7fefd9); BEFORE COMMIT
OK.

2026-11-20, 17:05. Gated at fd7fefd9: LEVEL 2 OK, LEVEL 3 OK (C-STEP 0
failures on 1,517 STEP lines), APPTRACES OK. This item, 027-02, 027-13
and 030's readme. Done.
