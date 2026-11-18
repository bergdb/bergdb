# 030-19. The three points of Codex review 3 in the contract package's checkers

Created 2026-11-18 by Frans Lundberg. Status: done.

The third independent review by Codex (the night of 17 November, of main
a16e5903; 006-30, section 6) found no false main theorem and three small new
points. Frans decided at 08:42 on 18 November that an agent fixes them
(006-31, D5: "D5, as recommended"). The points, as the review states them:

1. a delete bitmap beyond 64 bits is read as empty;
2. a PROBE line that fails, and a trace without its GET and SCAN lines,
   pass both checkers;
3. 030-09's "4.3 million" exceeds its own detailed total of 3,964,301.

Done by an agent of coord-1118 on the branch `030-19-codex3` from main
52459c9d, in a clone. No Java change; no statement and no proof changed.


# 1. The result

All three points are fixed. The first two are now faults of the trace's
wholeness (`completeFault`, Contract/Complete.lean), which both checkers run
and the contract checker's verdict includes, so each fails both checkers with
a message that names it; each has fault tests that passed main's checkers
and fail them now.

## 1.1 A bitmap wider than Java's

- **Cause.** `bitsOf` (Contract/Trace.lean) read only bits 0 to 63 of a
  `B b` klong (`List.range 64`), and neither the reader (`readKlongs`) nor
  the grammar (`klongToksOk`, 030-15) bounded b. A bit at 64 or above was
  dropped: the review's `B 18446744073709551616` (2^64) was read as an
  empty bitmap, and with a matching empty delete entry (`ADD 3 1 D 0`) the
  trace passed both checkers. (A bit 62 or 63 was read and failed W2, C1.)
- **What Java writes.** A delete bitmap has 62 bits, for the klongs 0 to 61
  (`Klong`, `Dag.MAX_NODE_SIZE` is 62), and `TraceExport.klongs` writes
  `klong & 0x3fffffffffffffff`: b < 2^62 always.
- **Fix: refused.** A `B b` klong with b of 2^62 or more fails the trace:
  the grammar (`isBitmap`, `bitmapBits`; `lineFault` says "a delete bitmap
  wider than Java's 62 bits (027-02, section 4)") and the reader
  (`readKlongs`: unreadable). And `bitsOf` now reads every bit of its number
  (`List.range (b.log2 + 1)`), proved: `mem_bitsOf_iff`, j is in `bitsOf b`
  exactly if bit j of b is set. 027-02, section 4 states the bound.

## 1.2 A PROBE line that fails, and reads left out

- **Cause.** 030-09 decided that PROBE lines do not fail the contract
  checker (run B's lines, which `tracecheck` checks), and 030-15's grammar
  takes `ok` and `fail` alike. The wholeness check (030-09) and the grammar
  (030-15) checked each line and the order of a transaction's lines, but
  not that a transaction has its reads; `readsOk` (Verdict.lean) is true of a
  transaction with no GET or SCAN line. So the two checkers passing
  certified neither that Java's run B and run E checks passed nor that
  Java's readers were tested (the review).
- **Fix, in `completeFault`:**
  - a `PROBE i fail ...` line fails the trace, as an `ERROR` line does
    ("a PROBE line that failed (a check of run B or run E)");
  - at `END i`, i > 0: exactly one SCAN line, at least one GET line, and
    as many GET lines as in every other transaction after `TX 0`. The
    exporter writes `gets=N` GET lines and one SCAN line after every record
    (`recordTree`, default N = 4, user transactions and reclaim's records
    alike; 027-02, section 4). N is not in the trace (the CONFIG line has no
    `gets=`), so the first transaction's count is the trace's.
- A trace exported with `gets=0` now fails both checkers; no script makes
  one.

## 1.3 The count of 030-09

030-09, section 1 said "No failure in 4.3 million transactions of the unit
tests and f-tests"; it now says 3.96 million, as its section 3 counts them:
"What it checked, one run of each": the unit tests 130,517 and the f-tests
3,833,784 transactions, 3,964,301 in all. The 4.3 million was the sum of
another run, section 4's `transcheck.sh` (132,288 and 4,158,103 in its log,
4,290,391). The f-tests' count differs from run to run: from 2,839,522 to
4,266,635 in the seven runs that 030-09's agent logged, and 1,890,105 in
the review's own run (with 128,960 in the unit tests, the "about 2 million"
of 006-30, section 6). No other maintained text has the number: 006-30's
progress line of 15:58 keeps it, as a record of that day.


# 2. The fault tests

Each new fault was run on main's checkers first (each passed: 9 WRONG in
`faults.sh`, 7 in `bridge-faults.sh`), then on the fixed ones (each fails).

`faults.sh` (the contract checker), on the good trace of 60 transactions
that it makes with Java, from TX 30 on:

- `bitmap64`: 2^64 added to the first bitmap of a KN line, so its bits 0
  to 63 are the same: read as the bitmap itself until now; fails (not
  whole: a delete bitmap wider than Java's 62 bits).
- `bitmap62`: 2^62 added: C1 caught it before (W2); fails now as not whole.
- `probefail`: `PROBE 30 fail wrong values after restart` before `END 30`;
  `probeok`: `PROBE 30 ok` there passes.
- `noreads`: every GET and SCAN line left out; `nogets`, `noscan`: TX 30's
  GET lines, its SCAN line; `oneget`: one GET line of TX 30.
- `s-bitmap`, `s-probefail`, `s-noreads`: the review's own three traces
  (`test/small.trace` changed, byte for byte the review's).

`bridge-faults.sh` (the bridge checker): `bitmap64` (the first bitmap of
`tree-small/mixed-1.trace`), `probe-fail` and `no-scan` in TX 5,
`no-reads`, and the review's three, `s-bitmap`, `s-probe-fail`,
`s-no-reads`.

Now `faults.sh` has 41 faults and 3 traces that pass, `bridge-faults.sh` 29
and 3, `faults-top.sh` (unchanged) 6 and 1.


# 3. Statements and pins

No theorem's statement and no proof changed. The definitions that
`contractVerdict_sound` and `checkVerdict_sound` rest on did: their
conclusion `completeFault lines = none` now also means no PROBE line that
fails, every bitmap below 2^62 and the reads of every transaction, and
`readTrace` refuses a wider bitmap. A new lemma, `mem_bitsOf_iff`
(Trace.lean), is not a main theorem. The pinned files changed: Trace.lean
and Complete.lean (definitions), Verdict.lean and ContractCheck.lean
(comments); `pin.sh` was run and `statements.pin` committed with them (4
hashes changed, 135 files pinned as before).


# 4. Gates

- `lake build` in `lean/contract/`: passes; 29 warnings, all in the old
  package (`lean/SIS`), as on main; none in this package.
- `lean/contract/gate.sh 52459c9d`: GATE OK: no sorry, admit,
  native_decide or axiom; 195 theorems, the standard three axioms only; no
  file changed outside the allowed paths; 124 files of the closure, 135
  pinned.
- `lean/contract/check.sh small drain reclaim`: CONTRACT OK, both
  checkers, 195 traces, 29,735 transactions (small 70 and 7,100, drain 110
  and 13,900, reclaim 15 and 8,735), 54 s; first `faults.sh`,
  `faults-top.sh` and `bridge-faults.sh`, each OK. Every transaction of
  the three sets has 4 GET lines and one SCAN line.
- Four traces with every kind of line, made here as 030-15 did (`probe=7`
  with `live=1`; `rune=random` with `ereads=4` and `erestart=9`;
  `rune=every` with `ereads`, `erestart` and `probe=13`; `retain=1` with
  `probe=5`): 490 transactions, 54 PROBE lines (all ok), FIRST, SLOT, the
  handles' lines and TOUCH; both checkers OK. The reclaim set has the FA,
  CUT and PHYSCUT lines.
- The review's four traces: its valid trace passes both checkers, the three
  faults fail both.
- No Java change, so no `java/before-commit.sh`.

The traces: the small and drain sets of 030-09's clone, and the reclaim set
of the review's (made at a16e5903; Java is the same on 52459c9d), copied into
this clone's `java/build/traces/`.


# 5. Decisions

- **Refuse a wider bitmap, and read every bit.** 027-02 says what a bit
  means and Java writes 62; a wider number is a fault of the exporter or of
  the file, as a line of the wrong form is (030-15's way). Reading every
  bit as well makes `bitsOf` right on its own, whatever the bound.
- **In `completeFault`, the trace's wholeness:** a line or a read missing,
  or Java's own report of a failure, is a trace that does not say what the
  run did; both checkers already run it, and it is in the contract
  checker's verdict, so `checkVerdict_sound` covers it with no new theorem.
- **PROBE lines that fail now fail**, against 030-09's decision (noted
  there): a trace with one is not a trace of a correct run, and the
  package's verdict should not pass it. `tracecheck` still checks them too.
- **The reads by count, not by `gets=` in the CONFIG line:** that needs a
  Java change, which the brief did not expect; the count rule catches the
  review's fault and the loss of a transaction's reads.


# 6. State note

Done; the last gated commit is in the Log. For whoever goes on:

- **Not changed, outside this package:** the old `treecheck`'s
  `bitsOfMask` (lean/Check/Tree.lean) reads bits 0 to 61 of a bitmap and
  passes over the rest. The level scripts run the contract checker on the
  same traces, which now refuses such a bitmap; a fix there belongs to the
  old package's owner (030-18 works in `lean/` today).
- **Seen, not changed:** `bridgecheck` counts a trace twice when it is both
  not whole and unreadable ("BRIDGE FAILED: 2 traces" for one); its exit
  status is right. BridgeCheck.lean is pinned.
- **Could follow:** `gets=N` in the CONFIG line, so that the checkers know
  N exactly.


Log
===

- 08:45 Started (an agent of coord-1118). Clone of main 52459c9d, branch
  `030-19-codex3`; the lake caches of the night's landing clone; Java built;
  the small and drain sets from 030-09's clone, the reclaim set from the
  review's.
- 08:48 The review's four traces on main's checkers: all pass both, as the
  review says. The new fault tests in `faults.sh` and `bridge-faults.sh`:
  9 and 7 WRONG on main's checkers.
- 08:55 The fixes (Trace.lean, Complete.lean): FAULTS OK, BRIDGE FAULTS OK;
  `check.sh small drain reclaim` CONTRACT OK (195 traces); four traces
  with every kind of line pass both checkers.
- 08:58 027-02, section 4; comments in ContractCheck.lean and Verdict.lean;
  `pin.sh`; `gate.sh 52459c9d` GATE OK.
- 09:00 030-09's count corrected (section 1; and its PROBE decision noted).
- 09:02 GATED 36cd14bb: the three points fixed, with fault tests;
  `gate.sh 52459c9d` GATE OK (195 theorems, the standard axioms only, the
  four pinned files changed listed for review); `check.sh small drain
  reclaim` CONTRACT OK on the commit (195 traces, 60 s).
